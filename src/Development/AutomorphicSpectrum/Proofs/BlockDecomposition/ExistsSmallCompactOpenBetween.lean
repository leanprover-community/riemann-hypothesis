module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem exists_compactOpen_between_mul_small
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  obtain ⟨K₆, hK₆o, -, hK₆s⟩ := hbase ((K₀ : Set G) ∩ N)
    (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c

  set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH
  have hHo : IsOpen (H : Set K₀) := hK₆o.preimage continuous_subtype_val
  haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set M : Subgroup K₀ := H.normalCore with hM
  have hMH : M ≤ H := Subgroup.normalCore_le H
  have hHc : IsClosed (H : Set K₀) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have hMc : IsClosed (M : Set K₀) := by
    have : (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun b => hHc.preimage (by fun_prop)
  haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H
  have hMo : IsOpen (M : Set K₀) := Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc

  set D : Subgroup K₀ := C.subgroupOf K₀ with hD
  set L : Subgroup K₀ := M ⊔ D with hL
  have hLo : IsOpen (L : Set K₀) := Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo
  have hLc : IsClosed (L : Set K₀) := OpenSubgroup.isClosed ⟨L, hLo⟩
  have himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀) := by
    ext x; simp [Subgroup.mem_map]
  refine ⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hK₀o.isOpenMap_subtype_val _ hLo
  · rw [himg]
    exact hLc.isCompact.image continuous_subtype_val
  · intro c hc
    refine ⟨⟨c, hC hc⟩, ?_, rfl⟩
    exact (le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)
  · exact Subgroup.map_subtype_le L
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
