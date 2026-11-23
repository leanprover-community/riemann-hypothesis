module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  first | exact @GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF | exact GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF | (intros; apply GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF <;> assumption)
