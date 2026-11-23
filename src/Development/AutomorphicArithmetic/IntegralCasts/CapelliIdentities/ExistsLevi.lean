module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolic

@[expose] public section

theorem UpperTheory.Reformulated.B.Gka3.exists_levi :
    ∀ {F E : Type} [_inst : Field F] [_inst_1 : NumberField F] [_inst_2 : Field E] [_inst_3 : NumberField E]
      [_inst_4 : Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
      {X Y : Matrix (Fin n) (Fin r) E},
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
          GlobalTheory.SiegelSet.IsWittFrame σ J X Y →
            ∀ (A : Type) [_inst_5 : CommRing A] [_inst_6 : Algebra F A] [TopologicalSpace A] (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J)
              (B : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
              B.BlockTriangular id →
                (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                                 Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B →
                  ∃ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J),
                    (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                          Matrix (Fin n) (Fin n) (TensorProduct F A E)) =
                        GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                            Matrix (Fin n) (Fin n) (TensorProduct F A E)) ∧
                      (∃ (d : Fin r → TensorProduct F A E),
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                                Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                              X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                            X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d) ∧
                        (∃ (d' : Fin r → TensorProduct F A E),
                            (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                               m) :
                                  Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                              Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d') ∧
                          (∃ (B' : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
                              B'.BlockTriangular id ∧
                                (∀ (i : Fin r), B' i i = (1 : TensorProduct F A E)) ∧
                                  (↑((GlobalTheory.AdelicU.matHom A σ J :
                                                       Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                     (m⁻¹ * p)) :
                                        Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B') ∧
                            ∀ (z : Fin n → TensorProduct F A E),
                              ((Formalism.UG.cT (↑σ : E →+* E) X * J).map
                                              (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec
                                          z =
                                  (0 : Fin r → TensorProduct F A E) →
                                ∃ (a : Fin r → TensorProduct F A E),
                                  ((↑((GlobalTheory.AdelicU.matHom A σ J :
                                                           Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                         (m⁻¹ * p)) :
                                                     Matrix (Fin n) (Fin n) (TensorProduct F A E)) -
                                                   (1 : Matrix (Fin n) (Fin n) (TensorProduct F A E))).mulVec
                                      z =
                                    (X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec a :=
  @GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi
