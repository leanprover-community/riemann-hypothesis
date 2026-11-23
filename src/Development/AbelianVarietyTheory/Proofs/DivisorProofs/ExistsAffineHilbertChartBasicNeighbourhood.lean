module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapBasicOpenBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapRestrictBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsBasisSpanEqTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsFiniteFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalkStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffineStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_basic_nhd : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  intro A B _ _ _ N r e Z y z
  obtain ⟨W₀, hW₀, hzW₀, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : Z.Opens) from trivial)
  let W : Z.affineOpens := ⟨W₀, hW₀⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.affineHilbertSections_finite_flat A B r Z y W
  obtain ⟨σ, f, hf, hbij⟩ := GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq Γ(Z, W₀) (GlobalTheory.HilbAff.Sec A B y W) N r
    (fun j => GlobalTheory.HilbAff.gen A B y W (e j)) (GlobalTheory.T.affineHilbertSections_basis_span_eq_top A B N r e Z y W) (GlobalTheory.T.affineHilbertSections_rankAtStalk A B r Z y W)
    (hW₀.primeIdealOf ⟨z, hzW₀⟩)
  have hD := (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f).2 hbij
  have hzf : z ∈ Z.basicOpen f := by
    have h1 : hW₀.primeIdealOf ⟨z, hzW₀⟩ ∈ hW₀.fromSpec ⁻¹ᵁ Z.basicOpen f := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hf
    have h2 := hW₀.fromSpec_primeIdealOf ⟨z, hzW₀⟩
    have h3 : hW₀.fromSpec (hW₀.primeIdealOf ⟨z, hzW₀⟩) ∈ Z.basicOpen f := h1
    rw [h2] at h3
    exact h3
  refine ⟨σ, Z.basicOpen f, hzf, ?_⟩
  rw [GlobalTheory.HilbAff.basic_iff]
  intro W'
  apply GlobalTheory.T.affineHilbertCoordinateMap_restrict_bijective
  exact GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine A B N r e σ Z y ⟨Z.basicOpen f, hW₀.basicOpen f⟩
    ⟨_, W'.2.image_of_isOpenImmersion (Z.basicOpen f).ι⟩ (Scheme.Opens.ι_image_le _ _) hD

end GlobalTheory.HilbAff
