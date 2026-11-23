module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.Opn

theorem exists_princ_loc_step : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), J = 1 → ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UPts σ J (v.adicCompletion F), (∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c) → y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n T f J bad S v hJ
  subst hJ
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ σ S.U S.U_open
  refine ⟨M, Nat.pos_of_ne_zero hM, fun y hy hc => ?_⟩
  choose C hC hyC using hc
  have hz := Formalism.UG.P.afsplitU_mem v σ 1 y 1 hy (one_mem _)
  have hzU : Formalism.UG.P.afsplitU v y 1 ∈ S.U := by
    refine hMU _ hz fun a b => ?_
    have hyab : (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + M • C a b := by
      rw [nsmul_eq_mul, ← hyC a b, Matrix.sub_apply, add_sub_cancel]
    have e : (((Formalism.UG.P.afsplitU v y 1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
        (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * Formalism.UG.P.afsplitIE v (C a b) := by
      rw [Matrix.sub_apply, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_apply, Units.val_one, hyab, map_add (f := _), map_nsmul,
        nsmul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
        ring
      · simp [Matrix.one_apply_ne hab]
    rw [e, ← mul_assoc, ← map_natCast (Formalism.L2.Col.iA F E), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, one_mul]
    exact Formalism.UG.P.afsplit_IE_int v _ (hC a b)
  have h := ((S.U_eq _).1 hzU).2 v
  rwa [Formalism.UG.P.afsplit_right1] at h

end GlobalTheory.Mem.Col2.AdT.Opn
