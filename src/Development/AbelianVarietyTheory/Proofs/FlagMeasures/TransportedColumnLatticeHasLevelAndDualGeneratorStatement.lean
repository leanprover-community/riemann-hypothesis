module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGenerator
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt) ∧ ∃ x₀ ∈ X.Lb, (VS D).hT (X.zu u) x₀ = 1 ∧ ∃ d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), Fintype.linearCombination D.host.E (qFr wt) d = x₀ + (((D.mem u).A.T : D.host.E))⁻¹ • X.zu u ∧ ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ a : 𝓞 D.host.E, y - (a : D.host.E) • d ∈ Mq wt := by
  first | exact @GlobalTheory.St.G.mlat_main | exact GlobalTheory.St.G.mlat_main | (intros; apply GlobalTheory.St.G.mlat_main <;> assumption)
