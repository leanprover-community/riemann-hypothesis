import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
import Formalism.LocalToGlobal.GlobalTheory.GL4.PNabla
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def liftWord {n : ℕ} (w : List (Fin n × Fin n × ℕ)) : List (Fin (n + 1) × Fin (n + 1) × ℕ) :=
  w.map fun x => (x.1.castSucc, x.2.1.castSucc, x.2.2)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def elemMat (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (t : R) : Matrix (Fin r) (Fin r) R :=
  fun c d => (if c = d then 1 else 0) + (if c = b ∧ d = a then t else 0)




def RowNat (R : Type) [CommRing R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) : Prop :=
  ∀ (g : Matrix (Fin n) (Fin n) R) (f f' : ↥(dualWeyl R n n σ)),
    (f' : MvPolynomial (Fin n × Fin n) R) = rowAct R g (f : MvPolynomial (Fin n × Fin n) R) →
      io f' = rowAct R (Formalism.BranchingDeterminantCap.extM R g) (io f)





def HwVal (R : Type) [CommRing R] {n : ℕ} (lam σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) : Prop :=
  ∀ h : ↥(dualWeyl R n n σ), (h : MvPolynomial (Fin n × Fin n) R) = hw R le_rfl σ →
    io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ lam) (fun i => (σ i : ℤ)) : ℤ) : R) • Formalism.BranchingDeterminantCap.xiB R lam σ


theorem map_initMinor_gen {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n s : ℕ} (I : Fin s → Fin r)
    (hs : s ≤ n) : map φ (initMinor R I hs) = initMinor S I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

theorem map_xiB {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam σ : Fin n → ℕ) :
    map φ (Formalism.BranchingDeterminantCap.xiB R lam σ) = Formalism.BranchingDeterminantCap.xiB S lam σ := by
  unfold Formalism.BranchingDeterminantCap.xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, map_initMinor_gen, map_initMinor_gen]




end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
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
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)









end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
