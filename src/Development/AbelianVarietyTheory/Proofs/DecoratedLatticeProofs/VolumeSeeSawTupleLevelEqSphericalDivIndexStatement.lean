module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolumeSeeSawTupleLevelEqSphericalDivIndex
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  first | exact @GlobalTheory.LevIdx.vol_level_eq | exact GlobalTheory.LevIdx.vol_level_eq | (intros; apply GlobalTheory.LevIdx.vol_level_eq <;> assumption)
