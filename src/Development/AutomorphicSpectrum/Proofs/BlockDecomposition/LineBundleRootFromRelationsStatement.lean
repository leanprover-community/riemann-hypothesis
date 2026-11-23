module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelations
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

theorem _root_.GlobalTheory.T.line_bundle_root_from_relations : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  exact @GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese
