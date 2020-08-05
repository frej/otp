/*
 * %CopyrightBegin%
 *
 * Copyright Ericsson AB 2000-2018. All Rights Reserved.
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
 */

#ifndef __BEAM_SELECT_TAG_H
#define __BEAM_SELECT_TAG_H

//#define BEAM_PROFILE_SELECT_TAG

extern uint8_t select_tag_table[1 << _TAG_IMMED2_SIZE]; /* in beam_emu.c */
extern uint8_t select_tag_table_header[1 << 4]; /* in beam_emu.c */

typedef enum {
    BEAM_ST_HEADER = 0,
    BEAM_ST_CONS,
    BEAM_ST_BOXED,
    BEAM_ST_PID,
    BEAM_ST_PORT,
    BEAM_ST_SMALL,
    BEAM_ST_ATOM,
    BEAM_ST_CATCH,
    BEAM_ST_NIL,
    BEAM_STH_TUPLE,
    BEAM_STH_FUN,
    BEAM_STH_BIG,
    BEAM_STH_FLOAT,
    BEAM_STH_REF,
    BEAM_STH_BIN,
    BEAM_STH_PID,
    BEAM_STH_PORT,
    BEAM_STH_MAP,
    BEAM_STH_OTHER,
    BEAM_ST_LAST
} beam_select_tag_type_t;

enum beam_select_tag_type_testname {
    STTT_ATOM = 0,
    STTT_LIST,
    STTT_BITSTR,
    STTT_BIN,
    STTT_FLOAT,
    STTT_FUNCTION,
    STTT_TUPLE,
    STTT_INT,
    STTT_NIL,
    STTT_NONEMPTY_LIST,
    STTT_NUMBER,
    STTT_MAP,
    STTT_BOOL,
    STTT_PID,
    STTT_UNKNOWN,
    NOOF_STTT
};

extern erts_atomic64_t gchain_counts[NOOF_STTT][NOOF_STTT][3];

extern void gchain_init(void);
extern const char *gchain_test_name(enum beam_select_tag_type_testname n);

#endif	/* __BEAM_SELECT_TAG_H */
