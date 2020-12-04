/*
 * %CopyrightBegin%
 *
 * Copyright Ericsson AB 2020-2020. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * %CopyrightEnd%
 *
 * The algorithm and source code for the cluster partitioning algorithm and jump
 * table building is taken from the LLVM switch lowering utilites which are
 * distributed under the Apache License v2.0 with LLVM Exceptions (See
 * https://llvm.org/LICENSE.txt for license information). The source code has
 * been changed to not use LLVM utility classes and adapted to the style
 * conventions of the Erlang JIT code generator.
 *
 * A person familiar with the LLVM switch lowering utilities will recognize the
 * find_jump_tables() method as a straight-forward copy of the corresponding
 * code in LLVM, but the concept of gap filling and search tables are unique to
 * the Erlang JIT code generator.
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */

#include "beam_asm.hpp"

extern "C"
{
#include "bif.h"
#include "beam_common.h"
#include "code_ix.h"
#include "export.h"
}

#include "adv_select.hpp"

#ifdef DEBUG_ADV_SELECT
std::ostream &operator<<(std::ostream &os, const SelectBuilder::Cluster &c) {
    switch (c.kind) {
    case SelectBuilder::Cluster::RANGE:
        os << "(range) [" << c.low << " <= " << c.high << "] -> " << c.dest;
        return os;
    case SelectBuilder::Cluster::JUMP_TABLE:
        os << "(jt)[" << c.low << " <= " << c.high
           << "] idx: " << c.jump_table_idx;
        return os;
    case SelectBuilder::Cluster::SEARCH_TABLE:
        os << "(st)[" << c.low << " <= " << c.high
           << "] idx: " << c.jump_table_idx;
        return os;
    }
    ASSERT(0);
    return os;
}
#endif /* DEBUG_ADV_SELECT */

unsigned SelectBuilder::Cluster::noof_values(SelectBuilder *sb) const {
    switch (kind) {
    case RANGE:
        if (dest == sb->default_dest)
            return 0;
        return high - low + 1;
    case JUMP_TABLE: {
        unsigned n = 0;
        for (auto i : sb->jump_tables[jump_table_idx])
            if (i != sb->default_dest)
                n++;
        return n;
    }
    case SEARCH_TABLE:
        return sb->search_table_dests[search_table_idx].size();
    default:
        erts_printf("ZZZZZZ %d\n", kind);
        ASSERT(0 && "Not implemented");
        return 0;
    }
}

UWord SelectBuilder::get_jump_table_range(UWord first, UWord last) {
    ASSERT(last >= first);
    const UWord low = clusters[first].low;
    const UWord high = clusters[last].high;

    // FIXME: A range of consecutive cases has 100% density, but only requires
    // one comparison to lower. We should discriminate against such consecutive
    // ranges in jump tables.
    UWord r = high - low;
    if (r > (ERTS_UWORD_MAX - 1) / 100)
        return (ERTS_UWORD_MAX - 1) / 100;
    return r + 1;
}

UWord SelectBuilder::get_jump_table_num_cases(const TotalCasesVec &total_cases,
                                              UWord first,
                                              UWord last) {
    ASSERT(last >= first);
    ASSERT(total_cases[last] >= total_cases[first]);
    return total_cases[last] - (first == 0 ? 0 : total_cases[first - 1]);
}

bool SelectBuilder::is_suitable_for_jump_table(UWord num_cases, UWord range) {
    const UWord min_density = erts_adv_select_jt_density;  // In percent
    const UWord max_jt_size = erts_adv_select_jt_max;

    if (erts_adv_select_no_jt)
        return false;

    return range <= max_jt_size && (num_cases * 100 >= range * min_density);
}

bool SelectBuilder::range_fits_in_word(UWord low, UWord high) {
    // XXXX This should be made platform neutral
    UWord BW = 64;
    UWord Range =
            high - low + 1; // XXXX There is probably an overflow hiding here

    return Range <= BW;
}

bool SelectBuilder::build_jump_table(unsigned first,
                                     unsigned last,
                                     BeamInstr default_dest,
                                     Cluster &cluster) {
    ASSERT(first <= last);

    unsigned num_cmps = 0;
    JumpTable table;

    for (unsigned i = first; i <= last; ++i) {
        const UWord &low = clusters[i].low;
        const UWord &high = clusters[i].high;
        num_cmps += (low == high) ? 1 : 2;
        if (i != first) {
            // Fill the gap between this and the previous cluster.
            const UWord &prev_high = clusters[i - 1].high;
            ASSERT(prev_high < low);
            UWord gap = low - prev_high - 1;
            for (uint64_t j = 0; j < gap; j++)
                table.push_back(default_dest);
        }
        UWord cluster_size = high - low + 1;
        for (uint64_t J = 0; J < cluster_size; ++J)
            table.push_back(clusters[i].dest);
    }

    jump_tables.push_back(table);
    cluster = Cluster::JumpTable(clusters[first].low,
                                 clusters[last].high,
                                 jump_tables.size() - 1);
    return true;
}

#ifdef DEBUG_ADV_SELECT

void SelectBuilder::dump_jumptables(std::ostream &os) {
    for (unsigned i = 0; i < jump_tables.size(); i++) {
        JumpTable &jt = jump_tables[i];
        os << "Jumptable " << i << " size: " << jt.size() << "\n\r";
        for (unsigned row = 0; row < jt.size(); row++) {
            os << "  " << row << ": " << jt[row] << "\n\r";
        }
    }
}

void SelectBuilder::dump_searchtables(std::ostream &os) {
    for (unsigned i = 0; i < search_table_dests.size(); i++) {
        SearchTableDests &ds = search_table_dests[i];
        SearchTableValues &vs = search_table_values[i];

        os << "Searchtable " << i << " size: " << ds.size() << "\n\r";
        for (unsigned row = 0; row < ds.size(); row++) {
            os << "  " << row << ": " << vs[row] << " -> " << ds[row] << "\n\r";
        }
    }
}

#endif /* DEBUG_ADV_SELECT */

void SelectBuilder::dump(std::ostream &os, std::string label) {
#ifdef DEBUG_ADV_SELECT
    os << "==== " << label << " ====\n\r" << clusters.size()
       << " clusters remains\n\r";
    for (auto &i : clusters)
        os << "  " << i << "\n\r";
    dump_jumptables(os);
    dump_searchtables(std::cerr);
#endif /* DEBUG_ADV_SELECT */
}

void SelectBuilder::find_jump_tables(const std::vector<ArgVal> &args) {
    ASSERT(args.size() > 2);

    const unsigned min_jt_entries = erts_adv_select_jt_min;
    const unsigned small_num_entries = min_jt_entries / 2;

    UWord low = untag(args[0].getValue()), high = low;
    BeamInstr dest = args[1].getValue();

    for (size_t i = 2; i < args.size(); i += 2) {
        if (dest == args[i + 1].getValue() &&
            high + 1 == untag(args[i].getValue())) {
            /* The current range can be expanded */
            high++;
        } else {
            /* The current cluster cannot be expanded further */
            clusters.push_back(Cluster::Range(low, high, dest));
            low = untag(args[i].getValue());
            high = low;
            dest = args[i + 1].getValue();
        }
    }
    clusters.push_back(Cluster::Range(low, high, dest));
    const int64_t n = clusters.size();

    /* total_cases[x] contains the number of cases in all clusters <= x */
    TotalCasesVec total_cases(n);
    for (unsigned i = 0; i < n; i++) {
        total_cases[i] = clusters[i].high - clusters[i].low + 1;
        if (i != 0)
            total_cases[i] += total_cases[i - 1];
    }

    UWord range = get_jump_table_range(0, n - 1);
    UWord num_cases = get_jump_table_num_cases(total_cases, 0, n - 1);
    ASSERT(num_cases < ERTS_UWORD_MAX / 100);
    ASSERT(range >= num_cases);

    if (is_suitable_for_jump_table(num_cases, range)) {
        Cluster jt_cluster;
        if (build_jump_table(0, n - 1, default_dest, jt_cluster)) {
            clusters[0] = jt_cluster;
            clusters.resize(1);
            return;
        }
    }

    // Split Clusters into minimum number of dense partitions. The algorithm
    // uses the same idea as Kannan & Proebsting "Correction to 'Producing Good
    // Code for the Case Statement'" (1994), but builds the MinPartitions array
    // in reverse order to make it easier to reconstruct the partitions in
    // ascending order. In the choice between two optimal partitionings, it
    // picks the one which yields more jump tables.

    // min_partitions[i] is the minimum nbr of partitions of Clusters[i..N-1].
    std::vector<unsigned> min_partitions(n);
    // last_element[i] is the last element of the partition starting at i.
    std::vector<unsigned> last_element(n);
    // partitions_score[i] is used to break ties when choosing between two
    // partitionings resulting in the same number of partitions.
    std::vector<unsigned> partitions_score(n);
    // For partitions_score, a small number of comparisons is considered as good
    // as a jump table and a single comparison is considered better than a jump
    // table.
    enum PartitionScores : unsigned {
        NoTable = 0,
        Table = 1,
        FewCases = 1,
        SingleCase = 2
    };

    // Base case: There is only one way to partition Clusters[n-1].
    min_partitions[n - 1] = 1;
    last_element[n - 1] = n - 1;
    partitions_score[n - 1] = PartitionScores::SingleCase;

    // Note: loop indexes are signed to avoid underflow.
    for (int64_t i = n - 2; i >= 0; i--) {
        // Find optimal partitioning of Clusters[i..n-1].
        // Baseline: Put Clusters[i] into a partition on its own.
        min_partitions[i] = min_partitions[i + 1] + 1;
        last_element[i] = i;
        partitions_score[i] =
                partitions_score[i + 1] + PartitionScores::SingleCase;

        // Search for a solution that results in fewer partitions.
        for (int64_t j = n - 1; j > i; j--) {
            // Try building a partition from Clusters[i..j].
            range = get_jump_table_range(i, j);
            num_cases = get_jump_table_num_cases(total_cases, i, j);
            ASSERT(num_cases < UINT64_MAX / 100);
            ASSERT(range >= num_cases);

            if (is_suitable_for_jump_table(num_cases, range)) {
                unsigned num_partitions =
                        1 + (j == n - 1 ? 0 : min_partitions[j + 1]);
                unsigned score = j == n - 1 ? 0 : partitions_score[j + 1];
                int64_t num_entries = j - i + 1;

                if (num_entries == 1)
                    score += PartitionScores::SingleCase;
                else if (num_entries <= small_num_entries)
                    score += PartitionScores::FewCases;
                else if (num_entries >= min_jt_entries)
                    score += PartitionScores::Table;

                // If this leads to fewer partitions, or to the same number of
                // partitions with better score, it is a better partitioning.
                if (num_partitions < min_partitions[i] ||
                    (num_partitions == min_partitions[i] &&
                     score > partitions_score[i])) {
                    min_partitions[i] = num_partitions;
                    last_element[i] = j;
                    partitions_score[i] = score;
                }
            }
        }
    }

    // Iterate over the partitions, replacing some with jump tables in-place.
    unsigned dst_idx = 0;
    for (unsigned first = 0, last; first < n; first = last + 1) {
        last = last_element[first];
        ASSERT(last >= first);
        ASSERT(dst_idx <= first);
        unsigned num_clusters = last - first + 1;

        Cluster cluster;
        if (num_clusters >= min_jt_entries &&
            build_jump_table(first, last, default_dest, cluster)) {
            clusters[dst_idx++] = cluster;
        } else {
            for (unsigned i = first; i <= last; ++i)
                std::memmove(&clusters[dst_idx++],
                             &clusters[i],
                             sizeof(clusters[i]));
        }
    }
    clusters.resize(dst_idx);
}

void SelectBuilder::find_search_tables() {
    // Iterate over the clusters, replacing unbroken sequences of
    // single-element RANGE clusters with search tables in-place.
    unsigned dst_idx = 0;
    for (unsigned first = 0; first < clusters.size();) {
        if (!clusters[first].is_single_value()) {
            if (first != dst_idx)
                std::memmove(&clusters[dst_idx],
                             &clusters[first],
                             sizeof(clusters[0]));
            first++;
            dst_idx++;
            continue;
        }

        unsigned next, last;
        // Gobble up as many single value clusters as we can
        for (next = first + 1, last = first;
             next < clusters.size() && clusters[next].is_single_value();
             next++, last++)
            ; // Empty

        if (last - first > 0) {
            SearchTableValues values;
            SearchTableDests dests;
            for (unsigned i = first; i <= last; i++) {
                ASSERT(clusters[i].low == clusters[i].high);
                values.emplace_back(clusters[i].low);
                dests.emplace_back(clusters[i].dest);
            }
            bool is_rightmost_cluster = last == (clusters.size() - 1);
            bool is_leftmost_cluster = first == 0;
            clusters[dst_idx++] = Cluster::SearchTable(
                    is_leftmost_cluster ? 0 : clusters[first].low,
                    is_rightmost_cluster ? ERTS_UWORD_MAX : clusters[last].high,
                    search_table_dests.size());
            search_table_values.push_back(values);
            search_table_dests.push_back(dests);
        } else {
            std::memmove(&clusters[dst_idx++],
                         &clusters[first],
                         sizeof(clusters[first]));
        }
        first = next;
    }
    clusters.resize(dst_idx);
}

void SelectBuilder::fill_gaps() {
    for (unsigned i = 0; i < clusters.size() - 1;) {
        if (clusters[i].high + 1 != clusters[i + 1].low) {
            clusters.insert(clusters.begin() + i + 1,
                            Cluster::Range(clusters[i].high + 1,
                                           clusters[i + 1].low - 1,
                                           default_dest));
        } else
            i++;
    }
    if (clusters[0].low != 0) {
        clusters.insert(clusters.begin(),
                        Cluster::Range(0, clusters[0].low - 1, default_dest));
    }
    if (clusters[clusters.size() - 1].high != ERTS_UWORD_MAX) {
        clusters.insert(clusters.end(),
                        Cluster::Range(clusters[clusters.size() - 1].high + 1,
                                       ERTS_UWORD_MAX,
                                       default_dest));
    }
}

SelectBuilder::SelectBuilder(UWord default_dest,
                             const std::vector<ArgVal> &args)
        : default_dest(default_dest),
          is_atoms_only(is_atom(args[0].getValue())) {
#ifdef DEBUG
    // Check that atoms are sorted
    if (is_atoms_only) {
        uint64_t last = args[0].getValue();
        for (unsigned i = 0; i < args.size(); i += 2) {
            ASSERT(last <= args[i].getValue());
        }
    }
#endif /* DEBUG */

#ifdef DEBUG_ADV_SELECT
    std::cerr << "==== Raw ====\n\r"
              << "default: " << default_dest << "\n\r";
    for (unsigned i = 0; i < args.size(); i += 2)
        std::cerr << "  " << args[i].getValue() << " -> "
                  << args[i + 1].getValue() << "\n\r";

#endif /* DEBUG_ADV_SELECT */
    find_jump_tables(args);
    dump(std::cerr, "After building jump tables");
    if (!erts_adv_select_no_st)
        find_search_tables();
    dump(std::cerr, "After building search tables");
    fill_gaps();
    dump(std::cerr, "After filling gaps");
}

UWord SelectBuilder::untag(UWord tagged) {
    return is_atoms_only ? atom_val(tagged) : unsigned_val(tagged);
}
