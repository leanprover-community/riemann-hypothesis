module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DetLatticeTensorIsDegOnMuTwDeg
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
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_datum_degree_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω), (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) → Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) → (∀ τ, LinearIndependent Ω (s τ)) ∧ (Lat.tens (fun τ => detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y (muTwDeg Hd B) (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) := by
  first | exact @LevelTowerAlt.det_lattice_tensor_isDegOn_muTwDeg | exact LevelTowerAlt.det_lattice_tensor_isDegOn_muTwDeg
