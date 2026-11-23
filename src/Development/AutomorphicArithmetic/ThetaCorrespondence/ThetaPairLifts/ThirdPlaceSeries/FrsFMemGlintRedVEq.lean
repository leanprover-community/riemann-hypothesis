module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiStdEqConstMulLocXi
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
namespace GlobalTheory.Fam.LevelFrames

theorem frsF_mem_glint_redV_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (j : ℕ), j + 1 ≤ B.R.m → ∀ (β : J.Ch₀ j) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
    Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 ∧
    ∀ x ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1, Formalism.L2.Col.redV P.1 (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P x) = Formalism.L2.Col.redV P.1 x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ n t J hJ j hj β P hP
  letI := GlobalTheory.Mem.Col2.starE B
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  refine ⟨?_, fun x hx => redV_eq_of_near (fun r s => ?_) hx⟩
  · have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hPv⟩ :=
      dif_pos hPv
    have h := (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hPv⟩).1
    have hN := (hJ.is.base j (by omega) β).2
    rw [e]
    intro x
    refine Iff.trans ?_ (h x)
    exact Iff.of_eq (congrArg (fun N => _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N) hN.symm)
  · rcases hj.eq_or_lt with h | h
    · exact _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv h β r s
    · have key := MidLoc.frame_cong hW.tr.ok (J.A.p0 j β).1.1 (hJ.std j h β ▸ (hJ.is.base j (by omega) β).1) P hPv r s
      rwa [if_congr Fin.ext_iff rfl rfl] at key
end GlobalTheory.Fam.LevelFrames
end
