module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

structure HTower (k : Type) [Field k] where
  Γ : Type
  Z : Scheme.{0}
  q : Z ⟶ Spec (CommRingCat.of k)
  Y : Γ → Scheme.{0}
  s : ∀ g, Y g ⟶ Z
  t : ∀ g, Y g ⟶ Z
  comm : ∀ g, t g ≫ q = s g ≫ q

variable {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]

abbrev HTower.geomZ : Scheme.{0} := GlobalTheory.Et.geom Ω H.q

def HTower.sΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.s g) rfl

def HTower.tΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g)


open Classical in
def hop (g : H.Γ) : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) := by
  classical
  exact if h : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T then h.choose else 0

def V (L : Type) [Field L] [Algebra ℚ_[l] L] {J : Type} (ι : J → H.Γ) (θ : J → L) :
    Submodule L (TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω)))) :=
  genEig L (fun j => hop l H Ω (ι j)) θ

def galV (L : Type) [Field L] [Algebra ℚ_[l] L] (σ : Ω ≃ₐ[k] Ω) :
    TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) →ₗ[L] TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) :=
  (galTot l Ω H.q σ).baseChange L

def HTower.idTower (k : Type) [Field k] : HTower k where
  Γ := Unit
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun _ => Spec (CommRingCat.of k)
  s := fun _ => 𝟙 _
  t := fun _ => 𝟙 _
  comm := fun _ => rfl

end GlobalTheory.GalV

end
