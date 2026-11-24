module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_functorial : ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K) (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  first | exact @GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | exact GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | (intros; apply GlobalTheory.CompanionTheory.KapRhoHom.rho_hom <;> assumption)
