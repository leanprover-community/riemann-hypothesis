module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownwardLevelMoveReachesKernelLattice
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

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.downwardLevelMove_reaches_kernelLattice : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : GL (Fin (D.R.N i)) D.host.E), loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (clsCrd D u i hi c) → (∀ (x : ↥(Ld D u i hi c')) (hx : γ.1 *ᵥ x.1 ∈ Lk A i hi v c), (D.fm u).fv i v c' (P.pr v c' x) = g (P.prk v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).L = loc (A.res v) (Lk A i hi v c) ∧ ∀ x ∈ loc (A.res v) (Lk A i hi v c), ((pc P v c').act (glE γ)).f x = g (locExt (A.res v) (Lk A i hi v c) (P.prk v c) x) := by
  first | exact @GlobalTheory.LevelHecke.pc_act_down | exact GlobalTheory.LevelHecke.pc_act_down | (intros; apply GlobalTheory.LevelHecke.pc_act_down <;> assumption)
