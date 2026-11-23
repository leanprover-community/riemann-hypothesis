module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam


theorem qj_place_ne_lev_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (i : Fin J.r) (P : HeightOneSpectrum (𝓞 B.fields.E)), P ∈ (B.primes X).vT u ∨ P ∈ (B.primes X).vGs → (J.G i).q.v ≠ P.under (𝓞 B.host.F) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha t J hJ i P hP
  have hv : (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
    obtain ⟨ε, hε, hs⟩ := (J.G i).q.above
    exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hs).symm
  have hQ : J.pl i ∈ I.SQ := I.Q_subset_SQ _ ((hW.tq.Q t (J.pl i)).1 (J.mem i))
  have hok : I.Ok := hW.tr.ok
  have key : ∀ PP : HeightOneSpectrum (𝓞 B.host.E), PP ∈ I.SQ → PP.under (𝓞 B.host.F) ≠ P.under (𝓞 B.host.F) := by
    intro PP hPP e
    apply (GlobalTheory.Mem.LevTwist.good_of_mem hok hPP).2.2.2
    rw [e]
    rcases hP with hP | hP
    · have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
      rw [(GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 (T_mem_vT hPr u ⟨P, hP⟩)]
      exact hok.T_mem u
    · exact GlobalTheory.Mem.LevTwist.plc_mem hok hP
  rw [hv]
  exact key (J.pl i) hQ
end GlobalTheory.Fam
end
