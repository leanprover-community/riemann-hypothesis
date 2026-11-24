module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.characterArgument_congr_rootEntrySum_mod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagChi.chiArg_sub_rootSum | exact GlobalTheory.FlagChi.chiArg_sub_rootSum | (intros; apply GlobalTheory.FlagChi.chiArg_sub_rootSum <;> assumption)
