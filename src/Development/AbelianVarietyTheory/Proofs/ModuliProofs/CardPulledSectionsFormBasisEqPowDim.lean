module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.SecRank

theorem card_eq_of_basisAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {T₁ T₂ T' : Over S} [Nontrivial Γ(T'.left, ⊤)] (h₁ : T' ⟶ T₁) (h₂ : T' ⟶ T₂) {n m : ℕ}
    {a : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T₁)} {b : Fin m → LB.Sec (Out.LPow G L (N : ℤ) T₂)}
    (ha : BasisAlong G L N h₁ a) (hb : BasisAlong G L N h₂ b) : n = m := by
  choose a' ha' _ using fun i => PolFrames.exists_pullSec G L N h₁ (a i)
  choose b' hb' _ using fun i => PolFrames.exists_pullSec G L N h₂ (b i)
  obtain ⟨l₁, s₁⟩ := (PolFrames.basisAlong_iff G L N h₁ hL ha').1 ha
  obtain ⟨l₂, s₂⟩ := (PolFrames.basisAlong_iff G L N h₂ hL hb').1 hb
  have e₁ := Module.finrank_eq_card_basis (Module.Basis.mk l₁ s₁.ge)
  have e₂ := Module.finrank_eq_card_basis (Module.Basis.mk l₂ s₂.ge)
  simpa using e₁.symm.trans e₂

theorem card_basis_eq_pow : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  intro _ hL R _ _ P N n b hN hb
  obtain ⟨V, hV, c, hc⟩ := hL.secBaseChangeAny (Sp R) P N hN (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (IsLocalRing.specializes_closedPoint x).mem_open V.isOpen hV
  subst hV'
  let χ : Sp R ⟶ (⊤ : (Sp R).Opens).toScheme := (Sp R).topIso.inv
  choose c' hc' _ using fun i => PolFrames.exists_pullSec P.A P.L N (Out.homAt χ) (c i)
  have H := (PolFrames.basisAlong_iff P.A P.L N (Out.homAt χ) P.isLB hc').2 (hc R χ c' hc')
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R)) : Over (Sp R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have key : ∀ (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (T : Over (Sp R)) (h : Over.mk f ⟶ T)
      (d : Fin (N ^ P.g) → LB.Sec (Out.LPow P.A P.L (N : ℤ) T)), BasisAlong P.A P.L N h d → n = N ^ P.g := by
    rintro _ rfl T h d hd
    exact card_eq_of_basisAlong P.A P.L P.isLB N _ h hb hd
  refine key (Out.baseAt χ).hom ?_ _ (Out.homAt χ) c H
  exact (congrArg (χ ≫ ·) (Category.comp_id (⊤ : (Sp R).Opens).ι)).trans (Sp R).toIso_inv_ι

end GlobalTheory.LN.SecRank
end
