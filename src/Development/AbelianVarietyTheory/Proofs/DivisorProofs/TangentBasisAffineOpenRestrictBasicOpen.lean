module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem spMap_res_chart {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  IsAffineOpen.map_fromSpec U.2 W.2 (homOfLE hW).op

theorem tanBasis_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w := by
  intro E _ _ _ H X t U W hW f _ n v hv hb
  open MonoidalCategory CartesianMonoidalCategory MonObj in
  open scoped CategoryTheory.Obj in
    let φ := (X.presheaf.map (homOfLE hW).op).hom
    let x := GlobalTheory.LogKS.chart U
    have := t.semi.comm
    have := t.semi.smooth
    have h₁ := isGrpPullback_pullback t.G x
    have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
    have h₃ := h₂.comp h₁
    have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
    have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
      Functor.isCommMonObj_obj
    obtain ⟨a₁, b₁⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t x _ _ h₁
    obtain ⟨-, b₃⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ h₃
    choose u hu using fun i => a₁ (v i) (hv i)
    have hbase : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hb⟩
    have hs : Smooth ((Over.pullback x).obj t.G).hom :=
      inferInstanceAs (Smooth (pullback.snd t.G.hom x))
    obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ _ _ _ h₂ hs n u hbase
    have e : Chart.dualMapR φ = dualMap φ := by
      ext a <;> rfl
    have key := (b₃ n u').1 hb'
    have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
        spMap (dualMap φ) ≫ v i := fun i => by
      rw [← Category.assoc, hu', e, Category.assoc, hu]
    rw [← funext e']
    rw [← spMap_res_chart U W hW]
    exact key.2

end GlobalTheory.LogKSDiv
