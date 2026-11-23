module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def castHQ {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : HQ l E n i ≃ₗ[ℚ_[l]] HQ l E n' i' := by
  subst hn; subst hi; exact LinearEquiv.refl _ _

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def idx (m : ℕ) (a : ℤ) : Finset ℕ := (Finset.range m).filter fun s => -a ≤ (s : ℤ) ∧ a + 2 * (s : ℤ) < m

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

def res (t : ℕ) (n i : ℤ) : HQ l (sch.obj (Ystr J t)) n i →ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J (t + 1))) n i :=
  ∑ j : Fin (t + 2), ((-1 : ℚ_[l]) ^ (j : ℕ)) • pullHQ l (sch.map (δ J t j)) n i

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

variable (a b w : ℤ)

end Galois

end GlobalTheory.EtC.WSS
