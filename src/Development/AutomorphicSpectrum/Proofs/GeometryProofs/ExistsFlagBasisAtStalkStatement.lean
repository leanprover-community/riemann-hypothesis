module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlagBasisAtStalk
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

theorem _root_.GlobalTheory.T.exists_flag_basis_at_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ b : ∀ s, Fin (labelRk D s) → 𝔐.Li, (∀ s (i : ℕ), flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) ∧ (∀ s (i : ℕ), ∀ e ∈ flagStep Ω (b s) i, e ∈ 𝔐.M.lat p → e ∈ Submodule.span (regAt 𝔐.ξ p) (b s '' {k | (k : ℕ) < i})) ∧ LinearIndependent Ω (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ Submodule.span Ω (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) = ⊤ ∧ 𝔐.M.lat p = Submodule.span (regAt 𝔐.ξ p) (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames | exact GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames <;> assumption)
