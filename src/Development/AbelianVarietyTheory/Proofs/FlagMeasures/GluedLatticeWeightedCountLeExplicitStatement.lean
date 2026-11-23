module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicit
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedLattice_weightedCount_le_explicit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  first | exact @GlobalTheory.GlueCount.glueSum_le | exact GlobalTheory.GlueCount.glueSum_le | (intros; apply GlobalTheory.GlueCount.glueSum_le <;> assumption)
