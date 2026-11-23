module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.constant_term_moderate_growth_inherited : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong <;> assumption)
