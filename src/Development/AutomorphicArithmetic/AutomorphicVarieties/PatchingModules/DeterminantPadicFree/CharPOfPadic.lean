module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.AcConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MaxIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hpl : p = l := by
    by_contra hne
    have hcop : l.Coprime p := (Nat.coprime_primes (Fact.out) hpp).2 (Ne.symm hne)
    have hu : IsUnit ((p : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
    have hu' := hu.map f
    rw [map_natCast, hpK] at hu'
    exact not_isUnit_zero hu'
  subst hpl
  exact hp

theorem UpperTheory.V.Pa.Det.kapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), PhiCond F.Γ l → Nonempty (Kap x) := by
  intro l _ F n x hΦ
  letI : Field x.K := x.field
  haveI : Finite x.K := x.fin
  letI : Algebra ℤ_[l] x.K := x.algZ
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  have hΦ0 : PhiCond F.G₀ l := UpperTheory.V.Pa.Det.phiSub l F.η.ker F.η_open hΦ
  have hρ : x.ρX x.A = fun g => mat x.ρ g := by
    funext g
    simp [UpperTheory.V.Pa.NP.ρX, Algebra.algebraMap_self]
  obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := UpperTheory.V.Pa.Det.selSub F (A := x.A) (R := x.A) x.t (x.ρX x.A)
    (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  have hSfg : S.FG := by
    refine UpperTheory.V.Pa.Det.matFg l (K := x.K) (G := F.G₀) (R := x.A) (1 : F.G₀ →* x.A) (mat x.ρ) S hΦ0
      ?_ ?_ ?_
    · intro N
      simp only [MonoidHom.one_apply]
      exact IsLocallyConstant.const (X := F.G₀) _
    · intro i j
      have h := x.cont i j
      simpa [PowerSeries.maximalIdeal_eq_span_X] using h
    · intro z hz
      rw [← SetLike.mem_coe, hS] at hz
      refine ⟨hz.2.1, ?_⟩
      intro g _ h _
      have e := hz.2.2.1 g h
      rw [hρ] at e
      simpa using e
  obtain ⟨g, κ, hmem, hind, hgen⟩ :=
    UpperTheory.V.Pa.Det.maxIndep x.t S B PowerSeries.X_irreducible hSfg
  have hsel : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    intro j
    rw [← hS]
    exact hmem j
  have hloc : ∀ j v, ∃ Y ∈ Od x.A x.A n x.a,
      LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v Y :=
    fun j v => (hsel j).2.2.2.2.2 v
  choose Y hYmem hYloc using hloc
  refine ⟨⟨g, κ, hsel, Y, hYmem, hYloc, ?_, ?_⟩⟩
  · intro c hc
    apply hind c
    rw [← SetLike.mem_coe, hB]
    exact hc
  · intro z hz
    rw [← hS] at hz
    obtain ⟨s, c, hsc⟩ := hgen z hz
    refine ⟨s, c, ?_⟩
    rw [← hB]
    exact hsc
