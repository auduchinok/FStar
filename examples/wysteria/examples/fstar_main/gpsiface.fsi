(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi FStar.OrdSet --admit_fsi FStar.IO --admit_fsi Smciface;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../../prins.fst ../ffi.fst ../wysteria.fsi gps.fst
 --*)

module Smciface

open Prins
open FStar.OrdSet

val gps: ps:prins -> p:prin{mem p ps} -> int -> Tot prin
