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

uint64_t g_FreedObjects = 0;

typedef void(*dealloc_f)(void* object);

typedef struct {
    const char* name;
    dealloc_f sys_dealloc;
} metadata_t;

typedef struct {
    uint64_t rc;
    dealloc_f sys_dealloc;
    dealloc_f usr_dealloc;
    metadata_t* metadata;
} refcount_t;

#ifdef INSTRUMENT_REFCOUNT
#include <stdio.h>
#define PRINT_POINTER printf("%s(%p)\n", __FUNCTION__, object)
#define PRINT_REFCOUNT printf("%s(%p)->rc == %" PRIu64 "\n", __FUNCTION__, object, object->rc)
#define PRINT(s) printf("%s(%p): %s\n", __FUNCTION__, object, s)
#define PRINT_COUNTER printf("%s(%p): g_FreedObjects = %" PRIu64 "\n", __FUNCTION__, object, g_FreedObjects)
#else
#define PRINT_POINTER
#define PRINT_REFCOUNT
#define PRINT(s)
#define PRINT_COUNTER
#endif

void __incref_f(refcount_t* object) {
PRINT_POINTER;
    if (object) {
        object->rc += 1;
        PRINT_REFCOUNT;
    }
}

uint64_t __getref_f(refcount_t* object) {
    if (object) {
        return object->rc;
    } else {
        return 0;
    }
}

void __decref_f(refcount_t* object) {
PRINT_POINTER;
    if (object) {
        if (object->rc == 0) {
            PRINT("dealloc");
            (*object->metadata->sys_dealloc)(object);
            g_FreedObjects += 1;
            PRINT_COUNTER;
        } else {
            object->rc -= 1;
            PRINT_REFCOUNT;
        }
    }
}
