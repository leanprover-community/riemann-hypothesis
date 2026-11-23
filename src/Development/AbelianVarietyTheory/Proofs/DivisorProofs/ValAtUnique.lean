module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_unique {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ)
    (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (p : (torsion G n).left) (c c' : M) (h : GlobalTheory.TorsSpec.ValAt G n ℓ w p c)
    (h' : GlobalTheory.TorsSpec.ValAt G n ℓ w p c') : c = c' := by
  haveI : Etale (torsion G n).hom := GrpTangent.etale_torsion G hn
  obtain ⟨t, ht, e⟩ := Flat.generalizingMap (torsion G n).hom
    (genericPoint_specializes ((torsion G n).hom p))
  obtain ⟨q, rfl⟩ : t ∈ Set.range ((torsion G n).left.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact ht
  let D := Spec ((torsion G n).left.presheaf.stalk p)
  let y : Sp (AlgebraicClosure (D.residueField q)) ⟶ D :=
    Spec.map (CommRingCat.ofHom (algebraMap (D.residueField q) (AlgebraicClosure (D.residueField q)))) ≫
      D.fromSpecResidueField q
  let g := y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).mpr ⟨ℓ v, Set.mem_univ _, v, rfl⟩
  have hg : Set.range g ⊆ Set.range ℓ := by
    rintro _ ⟨a, rfl⟩
    have hya : y a = q := by
      have : y a ∈ Set.range (D.fromSpecResidueField q) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have : g a = (torsion G n).hom ((torsion G n).left.fromSpecStalk p (y a)) := rfl
    rw [this, hya, e]
    exact hgen
  let z := IsOpenImmersion.lift ℓ g hg
  have hz : z ≫ ℓ = g := IsOpenImmersion.lift_fac ℓ g hg
  have h1 := h _ y z hz.symm
  have h2 := h' _ y z hz.symm
  exact hun _ z c c' (h1.symm.trans h2)

end GlobalTheory.TorsSpec
