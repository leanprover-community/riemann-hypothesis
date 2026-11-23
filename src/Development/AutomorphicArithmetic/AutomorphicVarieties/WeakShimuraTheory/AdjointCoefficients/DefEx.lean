module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CmplEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SpaceEx
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.defEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → Φ.noMu.Std l a ∧ Φ.noMu.IsRes ((residue Λ).comp a) c ∧ ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (P : PD Φ.ι Γ R), Φ.noMu.IsDef a c P := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS c hc
  haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  have hok : Φ.noMu.Ok ((residue Λ).comp a) :=
    ⟨hS.ok.mul, hS.ok.kill, hS.ok.dist, hS.ok.two, hS.ok.lc⟩
  have hS' : Φ.noMu.Std l a :=
    ⟨hok, hS.char, hS.cont, hS.phi, hS.closed, hS.phiv, fun _ _ hs => hs.elim⟩
  have hpair : ∀ {R : Type} [CommRing R] (b : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair b P → Φ.noMu.IsPair b P :=
    fun b P h => ⟨h.mult, h.kill, h.nrm, h.low, h.flag, fun _ _ hs => hs.elim⟩
  have hc' : Φ.noMu.IsRes ((residue Λ).comp a) c :=
    ⟨hpair _ c hc.pair, ⟨hc.res.diag, hc.res.char, hc.res.shape⟩, hc.cont⟩
  refine ⟨hS', hc', ?_⟩
  obtain ⟨X⟩ := spaceEx Φ.noMu l a hS'
  have hid : ∀ x : ResidueField Λ, res Λ (ResidueField Λ) x = x := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    exact (res Λ (ResidueField Λ)).commutes y
  have hmap : c.map ↑(res Λ (ResidueField Λ)) = c := by
    apply PD.ext
    · ext g i j
      simp [PD.map, mapRep, hid]
    · funext v
      ext i j
      simp [PD.map, hid]
  have hmax : maximalIdeal (ResidueField Λ) = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  have hlift : Φ.noMu.Lifts a c c := ⟨hc'.pair, by rw [hmax]; exact hc.cont, hmap⟩
  obtain ⟨x, hx⟩ := X.univ (ResidueField Λ) c c hc' hlift
  have hres : Φ.noMu.IsRes ((residue Λ).comp a) (X.P.map ↑x) := by rw [hx]; exact hc'
  obtain ⟨R, i1, i2, i3, f, hdef, -, -⟩ := cmplEx Φ.noMu l a hS' X x hres
  rw [hx] at hdef
  exact ⟨R, i1, i2, i3, X.P.map ↑f, hdef⟩
