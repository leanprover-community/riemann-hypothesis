module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWachModuleMapMatrixReductionComm
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

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_wachModule_map_matrix_reduction_comm : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  first | exact @GlobalTheory.WachMap.exists_mapMat_redHom | exact GlobalTheory.WachMap.exists_mapMat_redHom | (intros; apply GlobalTheory.WachMap.exists_mapMat_redHom <;> assumption)
