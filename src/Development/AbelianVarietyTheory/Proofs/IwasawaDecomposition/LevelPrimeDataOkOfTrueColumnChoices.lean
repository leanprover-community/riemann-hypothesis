module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAtZeroFree
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.LevelLaw

theorem ok_reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Ok T) :
    TDat.Ok (S := S.reRep pref) { A with } T :=
  { h with }

theorem tied_reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Tied T) :
    TDat.Tied (S := S.reRep pref) { A with } T :=
  { h with }

theorem atIn_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  intro B X I h u a
  obtain ⟨hX, hPr, -, -, hbig⟩ := base_fields_primes_ok B X
  have hQ : ∀ w ∈ I.Q a, ((B.primes X).T u : 𝓞 B.fields.E) ∉ w.asIdeal :=
    T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u)
  exact
    { T_prime := hPr.T_prime u
      card_ST := (hPr.vT_card u).trans B.fields_f
      card_res := fun P => (card_res P.1).trans (hPr.vT_norm u P.1 P.2)
      lev := fun j => ok_reRep (I.pref u a j) (tdatAt_ok I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u j)
      tied := fun j => tied_reRep (I.pref u a j) (tdatAt_tied I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u hQ j)
      psi_ne := fun P => psiWeil_ne_one (xiUnitAt_vT B X u P).2
      free0 := stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u hX hPr hbig (h.idx_ok a).zero_G
      duStar_pos := B.duStar_pos u
      Dstar_pos := B.Dstar_pos
      one_lt_gammaP := B.one_lt_gammaP }

end GlobalTheory.Mem.Col2.LevelLaw
