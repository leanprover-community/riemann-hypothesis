module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → (∀ i (hi : i + 1 ≤ B.R.m) α γ z, A.xi i hi α γ z = xiOff A i hi α γ z * ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∉ (B.primes X).vGs), B.embLL (locXi A i α γ P (homOf I l Z i hi z))) ∧ ∀ (c : Comm (I.rec7 l Z)) (hX : c.X = (I.rec7 l Z).sp.X) (v : VCom c) (Bs : GlobalTheory.Fam.Base c) PP (G : QGeo v Bs PP) χ (E : QExt G χ) hψ sg π (P : BadPr I a), ReadsAt A P E hψ sg π → ∀ j d (H : j + 1 + d = G.s) (hj : j + 1 ≤ B.R.m) (hj' : j + 1 < B.R.m) α γ (e' : XIx (Fin B.R.k) (Fin B.R.t) j ≃ Fin (B.R.N j)) (e : XIx (Fin B.R.k) (Fin B.R.t) (j + 1) ≃ Fin (B.R.N (j + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ x, (G.T E.δ E.tame E.η).entry G.ψk G.ν j d H (E.rep j (d + 1) (by omega) (π j α)) (E.rep (j + 1) d H (π (j + 1) γ)) (GlobalTheory.SymBridge.toLoc (G.q.pr.comp (incA (I.rec7 l Z))) e e' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)) = GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h j ((A.b0 j α).get hj) P) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) * GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h (j + 1) ((A.b0 (j + 1) γ).get hj') P) (B.R.N j + Formalism.L2.Col.cOf B.R j) * B.embLL (locXi A j α γ P x) := by
  exact @GlobalTheory.QTw.Join.xi_factor_and_entry
