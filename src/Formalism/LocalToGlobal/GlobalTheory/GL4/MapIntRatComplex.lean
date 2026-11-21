import Formalism.LocalToGlobal.GlobalTheory.GL4.ApplyWordMemDualGen
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def dpowR (R : Type) [CommRing R] (n c : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  lpMinor R (r := n) (n := n) n le_rfl le_rfl ^ c





def fockQLin {κ : Type} (G : MvPolynomial κ ℚ) : MvPolynomial κ ℚ →ₗ[ℚ] ℚ where
  toFun F := fockQ F G
  map_add' F F' := (Formalism.GradedWeylDivisibility.fockQBilin κ F F' G 0).1
  map_smul' c F := by rw [(Formalism.GradedWeylDivisibility.fockQBilin κ F 0 G c).2, smul_eq_mul, RingHom.id_apply]



theorem fockQ_hw_pos {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : 0 < fockQ (hw ℚ hn ν) (hw ℚ hn ν) :=
  (Formalism.GradedWeylDivisibility.fockQPos _ _ (hw ℚ hn ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ r n hn ν)

theorem intQ_apply (r n : ℕ) (q : MvPolynomial (Fin r × Fin n) ℤ) : intQ r n q = map (Int.castRingHom ℚ) q := rfl


end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
