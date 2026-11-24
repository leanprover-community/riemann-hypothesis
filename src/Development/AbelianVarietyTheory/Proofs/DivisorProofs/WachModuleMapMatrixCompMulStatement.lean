module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachModuleMapMatrixCompMul
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

theorem _root_.GlobalTheory.T.wachModuleMapMatrix_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  first | exact @GlobalTheory.WachPlace.isMapMat_comp_mul | exact GlobalTheory.WachPlace.isMapMat_comp_mul | (intros; apply GlobalTheory.WachPlace.isMapMat_comp_mul <;> assumption)
