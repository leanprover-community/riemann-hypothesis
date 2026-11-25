module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat

namespace GlobalTheory.HeatMod

section General

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {n : ℕ}

def combF (dd : Fin n → Fld Z) (c : Fin n → R) : Fld Z :=
  fun W f => ∑ a, constFn s W (c a) * dd a W f

def quadF (dd : Fin n → Fld Z) (M : Matrix (Fin n) (Fin n) R) : Fld Z :=
  fun W f => ∑ a, ∑ b, constFn s W (M a b) * dd a W (dd b W f)

end General

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {Ω : Type} [CommRing Ω] [StarRing Ω] [Module Ω Q.X]
  {oa : Q.OAct Ω} (Y : Ray oa)

def IsTorField (F : Fld Y.H.left) (ℓ : Q.X → R) : Prop :=
  IsField ⊤ F ∧ (∀ W r, F W (constFn Y.H.hom W r) = 0) ∧
    (∀ (α : Q.X) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f →
      F W f = constFn Y.H.hom W (ℓ α) * f) ∧
    ∀ (U : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)),
      W ≤ Y.q.left ⁻¹ᵁ U → F W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * F W f

end Raynaud

end GlobalTheory.HeatMod
