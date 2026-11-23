module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompat
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

theorem _root_.GlobalTheory.T.witt_level_morphism_cover_compat : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k) (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c)) (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory), stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj), (∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j)) → ∀ j, Function.Bijective (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  exact @GlobalTheory.CompanionTheory.FlatCoverGlue.glue
