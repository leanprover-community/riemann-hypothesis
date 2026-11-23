module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.IotaTwoZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def splitH (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (h : GHyp M g T T' TT Zh Z Zσ) : DG g Zh T T' ≃+ DD1 hs Z TT × DD1 hs Zσ TT :=
  splitQ hs h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

def thetaOf (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) :
    DG g Zh₁ T T' ≃+ DG g Zh₂ T T' :=
  (splitH hs h₁).trans ((AddEquiv.prodCongr θ₁ θ₂).trans (splitH hs h₂).symm)

def GamSplitP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1))
    (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂), KapEq Zh₁ Zh₂ →
    ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT), OLin hs θ₁ → OLin hs θ₂ →
      ((fun p => (thetaOf hs h₁ h₂ θ₁ θ₂ p.1, thetaOf hs h₁ h₂ θ₁ θ₂ p.2.1, p.2.2.1, p.2.2.2)) ''
          GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹)) Zh₁
            (algebraMap F E T) (algebraMap F E T') =
        GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹)) Zh₂
            (algebraMap F E T) (algebraMap F E T') ↔
      Match1 hs θ₁ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧
        Match1 hs θ₂ (ZZm g (Zh₁.map M.L.cj) T T') (ZZm g (Zh₂.map M.L.cj) T T'))

def FormSplitP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1))
    (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂),
    ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
      (∀ Y W Y₂ W₂ : Ix r → M.L.O,
          thetaOf hs h₁ h₂ θ₁ θ₂ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ →
          thetaOf hs h₁ h₂ θ₁ θ₂ (Submodule.Quotient.mk W) = Submodule.Quotient.mk W₂ →
          formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T)
              (algebraMap F E T') Y₂ W₂ -
            formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T)
              (algebraMap F E T') Y W ∈ M.L.O) ↔
        IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂

end Formalism.L2.SG.LocalCountModules.AlgGSplit
