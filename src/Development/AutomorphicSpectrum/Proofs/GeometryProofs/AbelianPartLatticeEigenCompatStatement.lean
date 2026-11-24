module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLatticeEigenCompat
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.abelian_part_lattice_eigen_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (Vl : Lat 𝔐.ξ 𝔐.Li) (m : ℕ) (U : Submodule Ω 𝔐.Li) (s : Fin m → 𝔐.Li) (sL : Fin m → V), Vl.IsVB m U → Vl.IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → IsValues 𝔐 z P MV s sL → LinearIndependent L sL → ∃ (T : FinitePlace L → Matrix (Fin m) (Fin m) L) (T' : FinitePlace L → Matrix (Fin m) (Fin m) Ω) (b' : FinitePlace L → Fin m → 𝔐.Li), (∀ v, Vl.IsFrameAt (b' v) ⟨z (primeOf v), 𝔐.all _⟩) ∧ (∀ v k, b' v k = ∑ k', T' v k' k • s k') ∧ (∀ v i j, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' v i j) (T v i j)) ∧ (∀ v, (T v).det ≠ 0) ∧ {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite ∧ ∀ x, x ∈ 𝔐.FibLat Vl z P MV ↔ x ∈ Submodule.span L (Set.range sL) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • sL j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame.fin_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame.fin_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame.fin_frame <;> assumption)
