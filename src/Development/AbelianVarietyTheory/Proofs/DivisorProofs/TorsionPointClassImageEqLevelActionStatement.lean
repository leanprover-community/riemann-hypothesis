module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelAction
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


theorem _root_.GlobalTheory.T.torsionPoint_class_image_eq_level_action : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).asIso.hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  first | exact @GlobalTheory.TorsSpec.class_move | exact GlobalTheory.TorsSpec.class_move | (intros; apply GlobalTheory.TorsSpec.class_move <;> assumption)
