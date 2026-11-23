module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (K.sh (K.le_refl k) (a k)) := hG _ _ (ptHom (K.jet k) (K.le_refl k)) rfl
    let j : K.Hom (K.triv k) (K.jet k) :=
      fromTriv (K.jet k) (K.le_refl k) (tszeSec dw)
        (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
        (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
          fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
            simp only [RingHom.comp_apply, sh_refl]
            exact tsze_expand h fun a ↦ dw a h⟩)
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ j rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (K.sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
