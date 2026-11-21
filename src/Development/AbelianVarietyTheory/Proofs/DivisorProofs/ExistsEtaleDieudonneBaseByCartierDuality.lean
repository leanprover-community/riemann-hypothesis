import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtDualOfConn

section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.dieuBase_isEt_of_isConn :
    ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)),
      ∃ Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt), Be.EtDual Bc :=
  fun p _ Bc => GlobalTheory.Dieu.exists_etDual_of_conn p Bc
end

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)), ∃ Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt), Be.EtDual Bc := by
  atlas_forward_decl GlobalTheory.dieuBase_isEt_of_isConn
