module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharacteristicDimensionZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Proportional

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup


theorem _root_.GlobalTheory.T.euler_characteristic_dimension_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = (0 : ℕ) → ∀ a : Fin 0 → Fin (m + 1) → ℤ, chi (ZMod p) (structureModule Z) = geoNum 0 (ptIdeal (f (genericPoint Z))) a := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.VertBase.chi_eq_geoNum | exact GlobalTheory.CompanionTheory.MixZ.VertBase.chi_eq_geoNum | (intros; apply GlobalTheory.CompanionTheory.MixZ.VertBase.chi_eq_geoNum <;> assumption)
