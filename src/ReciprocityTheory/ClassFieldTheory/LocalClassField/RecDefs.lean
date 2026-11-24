module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

abbrev GKab : Type := TopologicalAbelianization (GK p K)

def toAbK : GK p K →* GKab p K := QuotientGroup.mk' _

structure IsAbLK : Prop where
  le : K ≤ L
  fin : FiniteDimensional ℚ_[p] L
  comm : commutator (GK p K) ≤ subG p K L

def normHom : KbarMult p →+ KbarMult p :=
  ∑ᶠ c : GK p K ⧸ subG p K L, (kbarRep p K c.out).toAddMonoidHom

def normSub : AddSubgroup (KbarMult p) := (multOf p L).map (normHom p K L)

def normGrp : Subgroup Kˣ := AddSubgroup.toSubgroup' ((normSub p K L).comap (ofK p K))

theorem mem_normGrp_iff (x : Kˣ) :
    x ∈ normGrp p K L ↔ ∃ y ∈ multOf p L, normHom p K L y = ofK p K (Additive.ofMul x) := Iff.rfl

def IsArtinK (Art : Kˣ →* GKab p K) : Prop :=
  Continuous Art ∧ Function.Injective Art ∧ DenseRange Art ∧
  (∀ π : Kˣ, vK p K π = 1 → ∀ g : GK p K, toAbK p K g = Art π → IsFrob p K g) ∧
  ∀ L, IsAbLK p K L →
    (∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧ g'⁻¹ * g ∈ subG p K L) ∧
    ∀ (x : Kˣ) (g : GK p K), toAbK p K g = Art x → (g ∈ subG p K L ↔ x ∈ normGrp p K L)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
