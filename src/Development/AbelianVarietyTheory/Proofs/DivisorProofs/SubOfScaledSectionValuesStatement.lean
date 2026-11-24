module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValues
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

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


theorem _root_.GlobalTheory.T.sub_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  first | exact @GlobalTheory.HeatSym.VS.sub | exact GlobalTheory.HeatSym.VS.sub | (intros; apply GlobalTheory.HeatSym.VS.sub <;> assumption)
