(* Copyright 2023 Enrico Granata *)
(* *)
(* Licensed under the Apache License, Version 2.0 (the "License"); *)
(* you may not use this file except in compliance with the License. *)
(* You may obtain a copy of the License at *)
(*  *)
(*     http://www.apache.org/licenses/LICENSE-2.0 *)
(*  *)
(* Unless required by applicable law or agreed to in writing, software *)
(* distributed under the License is distributed on an "AS IS" BASIS, *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and *)
(* limitations under the License. *)

func main() ret int64 {
    func magic_number() ret int64 {
        return 1;
    };

    let x = magic_number() + magic_number();

    func magic_number() ret int64 {
        return 2;
    };

    let y = magic_number();

    return x - y;
}
