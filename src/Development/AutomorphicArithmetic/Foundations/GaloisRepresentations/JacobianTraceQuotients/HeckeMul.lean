module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem rep_mul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (a b : G) (w : V) : π (a * b) w = π a (π b w) := by
  rw [map_mul, Module.End.mul_apply]

private theorem exists_unipotent_eq_of_mem_iwLev_of_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (K : Subgroup (GL (Fin n) k)) (hK : IwLev K) (t : Fin n → kˣ) (ht : Dom t) (v : V)
    (hv : v ∈ fixed π K) (g : GL (Fin n) k) (hg : g ∈ K) :
    ∃ u ∈ K ⊓ unipB k (Fin n),
      π g (π (diagT k (Fin n) t) v) = π u (π (diagT k (Fin n) t) v) := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact g hg
  refine ⟨u, hu, ?_⟩
  have h1 : ∀ x : K, π x v = ((1 : K →* ℂˣ) x : ℂ) • v := hv
  have hfix : ∀ h ∈ K, π h v = v := fun h hh => by simpa using h1 ⟨h, hh⟩
  have hc' := hK.low t ht c hc
  have hcomm : diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d := by
    rw [← map_mul, ← map_mul, mul_comm]
  have key : u * diagT k (Fin n) d * c * diagT k (Fin n) t =
      u * diagT k (Fin n) t * (diagT k (Fin n) d *
        ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t)) := by
    calc u * diagT k (Fin n) d * c * diagT k (Fin n) t
        = u * (diagT k (Fin n) d * diagT k (Fin n) t) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by group
      _ = u * (diagT k (Fin n) t * diagT k (Fin n) d) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by rw [hcomm]
      _ = _ := by group
  rw [← rep_mul π (u * diagT k (Fin n) d * c), key, rep_mul π (u * diagT k (Fin n) t),
    rep_mul π (diagT k (Fin n) d), hfix _ hc', hfix _ hd, rep_mul]

theorem UpperTheory.Gal.Join.heckeMul :
    UpperTheory.Gal.Join.HeckeMul := by
  unfold UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep
  intro k _ _ _ _ n V _ _ π K hK e he t ht v hv
  have hN : ∀ u ∈ K ⊓ unipB k (Fin n), ∀ w : V,
      (twKer π (unipB k (Fin n)) 1).mkQ (π u w) = (twKer π (unipB k (Fin n)) 1).mkQ w := by
    intro u hu w
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨u, (Subgroup.mem_inf.mp hu).2⟩, w, by simp⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · have h2 := he.lin V (e.comp (π (diagT k (Fin n) s))) (π (diagT k (Fin n) t) v) ?_
    · simp only [LinearMap.comp_apply] at h2
      rw [h2, map_mul, rep_mul]
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      simp only [LinearMap.comp_apply]
      rw [hgu, ← rep_mul π (diagT k (Fin n) s) u,
        show diagT k (Fin n) s * u =
          (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹) * diagT k (Fin n) s by group,
        rep_mul π (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹),
        he.inv _ (hK.up s hs u hu)]
  · have h3 := he.lin _ (twKer π (unipB k (Fin n)) 1).mkQ (π (diagT k (Fin n) t) v) ?_
    · exact h3.trans rfl
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      rw [hgu, hN u hu]
