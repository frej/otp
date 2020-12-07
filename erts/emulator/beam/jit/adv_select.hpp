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

#ifndef _ASM_ADV_SELECT_H
#define _ASM_ADV_SELECT_H

#include <vector>
#include <iostream>
#include <cstring>
#include <memory>
#include <algorithm>

//#define DEBUG_ADV_SELECT

class ArgVal;

class SelectBuilder {
public:
    struct Cluster;

    typedef std::vector<UWordNA> JumpTable; // BeamInstr carries alignment
    typedef std::vector<JumpTable> JumpTableVec;
    typedef std::vector<Cluster> ClusterVec;
    typedef std::vector<unsigned> TotalCasesVec;
    typedef UWordNA SearchTableValue;
    typedef UWordNA SearchTableDest;
    typedef std::vector<SearchTableValue> SearchTableValues;
    typedef std::vector<SearchTableDest> SearchTableDests;

    UWord default_dest;
    bool is_atoms_only;

    ClusterVec clusters;
    JumpTableVec jump_tables;
    std::vector<SearchTableValues> search_table_values;
    std::vector<SearchTableDests> search_table_dests;

    struct Cluster {
        enum { RANGE, JUMP_TABLE, SEARCH_TABLE } kind;

        /* All values x, low <= x <= high, branches to dest. */
        UWord low, high;
        BeamInstr dest;

        union {
            unsigned jump_table_idx;
            unsigned search_table_idx;
        };

        static Cluster Range(UWord low, UWord high, BeamInstr dest) {
            Cluster c;
            c.kind = RANGE;
            c.low = low;
            c.high = high;
            c.dest = dest;
            return c;
        }

        static Cluster JumpTable(UWord low, UWord high, unsigned idx) {
            Cluster c;
            c.kind = JUMP_TABLE;
            c.low = low;
            c.high = high;
            c.jump_table_idx = idx;
            return c;
        }

        static Cluster SearchTable(UWord low, UWord high, unsigned idx) {
            Cluster c;
            c.kind = SEARCH_TABLE;
            c.low = low;
            c.high = high;
            c.search_table_idx = idx;
            return c;
        }

        // Return true if this is a single-element cluster
        bool is_single_value() const {
            return kind == RANGE && high == low;
        }

        bool has_single_dest() const {
            return kind == RANGE; // XXXX
        }

        BeamInstr get_single_dest() const {
            ASSERT(has_single_dest());
            switch (kind) {
            case RANGE:
                return dest;
            default:
                ASSERT(0 && "Not implemented");
                return dest;
            }
        }

        unsigned noof_values(SelectBuilder *sb) const;
    };

#ifdef DEBUG_ADV_SELECT
    friend std::ostream &operator<<(std::ostream &os, const Cluster &c);
#endif /* DEBUG_ADV_SELECT */

private:
    UWord untag(UWord tagged);
    UWord get_jump_table_range(UWord first, UWord last);
    UWord get_jump_table_num_cases(const TotalCasesVec &total_cases,
                                   UWord first,
                                   UWord last);
    bool is_suitable_for_jump_table(UWord num_cases, UWord range);
    bool range_fits_in_word(UWord low, UWord high);

    bool build_jump_table(unsigned first,
                          unsigned last,
                          BeamInstr default_dest,
                          Cluster &cluster);

    void find_jump_tables(const std::vector<ArgVal> &args);
    void find_search_tables();
    void fill_gaps();

    void dump(std::ostream &os, std::string label);

#ifdef DEBUG_ADV_SELECT
    void dump_jumptables(std::ostream &os);
    void dump_searchtables(std::ostream &os);
#endif /* DEBUG_ADV_SELECT */

    friend unsigned Cluster::noof_values(SelectBuilder *sb) const;

public:
    SelectBuilder(UWord default_dest, const std::vector<ArgVal> &args);

    const ClusterVec &get_clusters() const {
        return clusters;
    };

    UWord get_default_dest() const {
        return default_dest;
    };

    JumpTable &get_jump_table(unsigned idx) {
        return jump_tables[idx];
    }
    SearchTableValues &get_search_table_values(unsigned idx) {
        return search_table_values[idx];
    }
    SearchTableDests &get_search_table_dests(unsigned idx) {
        return search_table_dests[idx];
    }

    bool atoms_only() {
        return is_atoms_only;
    }

    UWord tag(UWord tagged);
};

std::ostream &operator<<(std::ostream &os, const SelectBuilder::Cluster &c);

#endif /* _ASM_ADV_SELECT_H */
