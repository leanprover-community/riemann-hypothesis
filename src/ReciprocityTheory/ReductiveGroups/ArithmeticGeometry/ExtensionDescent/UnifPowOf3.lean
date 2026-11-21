import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

structure UnifPowOf2 {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G)
    extends UnifPowOf pD pA pG U' U where

  t_pr : ∀ (e : ℕ) (x : D'.toPre.X),
    ∃ hψ : ∀ (i : Fin j) (k : Fin 4),
        D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫
          (pD.pw.pr i).left =
        ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫
          D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k,
      LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x)
        (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i =>
          GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left
            ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i)
            ((U.gt e).t (pD.xe x i))))

def UnifPowSt2 : Prop :=
  ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (j : ℕ)
    (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j),
    ∃ U' : Unif I D' A' G', Nonempty (UnifPowOf2 pD pA pG U' U)

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

def UnifPowOf2.WPr {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j}
    {pG : IsPowGrp G' G j} {U' : Unif I D' A' G'} {U : Unif I D A G}
    (P : UnifPowOf2 pD pA pG U' U) : Prop :=
  ∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι)
    (jNL : Fin j → U.LG.L.ι),
    res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) :
        (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓
          (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U
            (fun _ => jM', fun _ => jL') ⊓
          (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ
            (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U
              (fun _ => jNM i, fun _ => jNL i)) ⊓
          (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤
        (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM'))
      (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) *
    res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right))
      ((U'.w e).s (fun _ => jM', fun _ => jL')) =
    (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i)))
      (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _
        ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) *
    res (X := (thickObj R I e G').left) inf_le_right
      (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (P.wL.s (jNL, jL')))

structure UnifPowOf3 {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G)
    extends UnifPowOf2 pD pA pG U' U where

  w_pr : toUnifPowOf2.WPr

def UnifPowSt3 : Prop :=
  ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (j : ℕ)
    (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j),
    ∃ U' : Unif I D' A' G', Nonempty (UnifPowOf3 pD pA pG U' U)

end ReciprocityTheory.ChartRestriction.G.Out
end
end
