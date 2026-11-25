module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
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
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm GlobalTheory.QTw
open scoped TensorProduct Classical
namespace GlobalTheory.QTw

theorem frsF_base_eq_self : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀), A.Is → I.Ok → ∀ (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (i : ℕ), i ≤ B.R.m → ∀ (β : Ch₀ i), (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1) → ∀ (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P x = x := by
  intro B X I l Z u a Ch₀ A hA hI P hP i hi β hv x
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
    intro hm
    apply GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2
    have := Ideal.mem_comap.1 hm
    simpa [map_natCast] using this
  have hk := hv _ hT
  have hpt := (hA.base i hi β).1
  have hfr := hpt.fr ⟨P.1, hSQ⟩
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩]
  set f := (extTo I.SQ (A.p0 i β).1.1).fr ⟨P.1, hSQ⟩ with hf
  have key : ∀ j : Fin (B.R.N i), f (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext r
    have h1 := hfr r j
    rw [GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_one P.1 hk r j] at h1
    apply (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective
    rw [← h1, Pi.single_apply]
    split_ifs <;> simp
  have : (f : Formalism.L2.Col.Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N i)) = LinearMap.id :=
    LinearMap.pi_ext' fun j => LinearMap.ext_ring (key j)
  exact congrArg (fun g => g x) this

end GlobalTheory.QTw
