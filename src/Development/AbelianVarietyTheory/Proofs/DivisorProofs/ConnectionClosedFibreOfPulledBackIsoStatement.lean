module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreOfPulledBackIso
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.connection_closedFibre_of_pulledBack_iso : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj d q := by
  first | exact @GlobalTheory.PotIso.conn_of_iso | exact GlobalTheory.PotIso.conn_of_iso | (intros; apply GlobalTheory.PotIso.conn_of_iso <;> assumption)
