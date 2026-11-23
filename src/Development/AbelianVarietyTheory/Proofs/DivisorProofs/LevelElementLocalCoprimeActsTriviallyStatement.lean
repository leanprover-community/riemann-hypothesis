module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelElementLocalCoprimeActsTrivially
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelElement_local_coprime_acts_trivially : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  first | exact @GlobalTheory.FrameTriv.triv_of_isLocEnv | exact GlobalTheory.FrameTriv.triv_of_isLocEnv | (intros; apply GlobalTheory.FrameTriv.triv_of_isLocEnv <;> assumption)
