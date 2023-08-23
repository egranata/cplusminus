// Copyright 2023 Enrico Granata
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <inttypes.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

static void fail() {
#if __has_builtin(__builtin_trap)
  __builtin_trap();
#else
  abort();
#endif
}

void __assert_f(uint32_t condition, const char* file, uint32_t line) {
    if (condition == 0) {
        fprintf(stderr, "error: assertion failed at %s:%" PRIu32 "\n", file, line);
        fail();
    }
}
