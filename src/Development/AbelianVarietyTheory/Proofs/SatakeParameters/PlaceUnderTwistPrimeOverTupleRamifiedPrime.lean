module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.UnderQp

theorem mem_QE_of_heq {B : Base} {X : PreX B.toPre} (I : TC B X) {Xf : Fields} (hX : Xf = B.fields) {S : Set ℕ} (hS : S = I.S)
    {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} (hsel : HEq sel I.sel)
    {tup : I.ι → Tup Xf.F Xf.E Xf.K S} (htup : HEq tup I.tup) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hP : P ∈ I.Q a) (q : ℕ) (hq : (q : 𝓞 B.fields.E) ∈ P.asIdeal) :
    ∃ P' ∈ QE sel (tup a : Chr Xf.F Xf.E Xf.K), (q : 𝓞 Xf.E) ∈ P'.asIdeal := by
  subst hX
  subst hS
  cases hsel
  cases htup
  exact ⟨P, hP, hq⟩

theorem underQ_qp : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), I.UnderQ a v → ∃ q ∈ Y.Qp a, ((q : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
  intro B X I _ _ l Z L hT Gi Gl K Y cX ex t hSK a v hv
  obtain ⟨P, hP, hPv⟩ := hv
  have hN1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  set q := (Ideal.absNorm P.asIdeal).minFac with hqdef
  have hqp : q.Prime := Nat.minFac_prime hN1
  have hqP : (q : 𝓞 B.fields.E) ∈ P.asIdeal :=
    GlobalTheory.KerTie.natCast_mem_of_prime_dvd_absNorm P hqp (Nat.minFac_dvd _)
  refine ⟨q, ?_, ?_⟩
  · exact (t.Q_rec a q).2 ⟨hqp, mem_QE_of_heq I hSK.X_eq hSK.S hSK.sel hSK.tup a P hP q hqP⟩
  · rw [← hPv]
    show (q : 𝓞 B.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))
    rw [Ideal.mem_comap, map_natCast]
    exact hqP

end GlobalTheory.TwU.UnderQp
