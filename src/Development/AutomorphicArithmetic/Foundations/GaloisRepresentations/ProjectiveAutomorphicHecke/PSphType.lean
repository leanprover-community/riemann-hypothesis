module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSphType_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.SphType := by
  intro hIC hLC E _ _ _ n π w hw
  refine ⟨?_, ?_⟩
  · rintro ⟨B, σ, ⟨-, f, hf0, hfV, hf⟩, hB⟩
    have hker : LinearMap.ker f = ⊥ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => ?_)).resolve_right
        fun h => hf0 (LinearMap.ker_eq_top.1 h)
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hf ⟨(locF hw g).1, locF_mem hw g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, cLoc_locF] at h1
      rw [h1, hv, map_zero]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hv
    have hφ0 : f v ≠ 0 := fun h => hv0 (LinearMap.ker_eq_bot.1 hker (h.trans (map_zero f).symm))
    have key : ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x (f v) = f v := by
      intro x hx hk
      have h1 := hf ⟨x, hx⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
      rw [← h1, hfix _ hk]
    obtain ⟨-, -, -, -, hcc, hloc⟩ := hLC E n w hw
    refine ⟨⟨f v, hfV v, hφ0, fun x hx h => ?_⟩, ⟨f v, hfV v, hφ0, fun x hx h => ?_⟩⟩
    · simpa using key x hx h
    · rw [hloc] at hx
      have h2 := hIC E n (ofU ⟨x, (Subgroup.mem_inf.1 hx).1⟩) (cj w) (by rw [sim_ofU]; exact one_mem _)
        (by rw [comp_ofU]; exact h)
      rw [hcc, comp_ofU] at h2
      simpa using key x hx h2
  · rintro J χ ⟨φ, hφ, h0, hact⟩
    have hlev := (π.isAut.aut φ hφ).level
    have hc : Continuous fun k : J => (locF hw k.1 : finU (E := E) (n := n)) := by
      have h1 : Continuous fun k : GLw n w => (locF hw k : finU (E := E) (n := n)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp (locE hw).symm.continuous) _
      exact h1.comp continuous_subtype_val
    have hset : {k : J | χ k = 1} = (fun k : J => (locF hw k.1 : finU (E := E) (n := n))) ⁻¹' {k : finU (E := E) (n := n) | RU E n k φ = φ} := by
      ext k
      have hk : cLoc w (locF hw k.1).1 ∈ J := by rw [cLoc_locF]; exact k.2
      have h1 := hact (locF hw k.1).1 (locF_mem hw k.1) hk
      have h2 : (⟨cLoc w (locF hw k.1).1, hk⟩ : J) = k := Subtype.ext (cLoc_locF hw k.1)
      rw [h2] at h1
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [h1]
      constructor
      · intro h; rw [h]; simp
      · intro h
        have h3 : ((χ k : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ h0 (by simpa using h)
        exact Units.ext h3
    rw [hset]
    exact hlev.preimage hc
