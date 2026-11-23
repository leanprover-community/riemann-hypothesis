module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormula
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.flag_line_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y) (x : CMType H × Fin (D.p + D.q) → HermLine J) (e : CMType H × Fin (D.p + D.q) → Ω), (∀ r, IsSmoothHerm (x r)) → Fl.RootLines (fun r => (x r).a) e → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ 𝔐.X), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier) (A : FlagPair B (CMType H) D.p D.q), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ((∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i)) → (∀ τ (i : Fin D.p), |Ht.lineHt (x (τ, Fin.castAdd D.q i)) L w - (A.W τ).grDeg i| ≤ C) ∧ ∀ τ (i : Fin D.q), |Ht.lineHt (x (τ, Fin.natAdd D.p i)) L w + (A.S τ).grDeg i.rev| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.root_height | exact GlobalTheory.CompanionTheory.Ar.RootHt.root_height | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.root_height <;> assumption)
