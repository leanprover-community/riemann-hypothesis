import Mathlib

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Filter Topology

open Set



def discI (a R : ℝ) : ℝ :=
  ∫ z in Metric.ball (0 : ℂ) R, Real.exp (-(a * ‖z‖ ^ 2))








end ReciprocityTheory.GeometryOfNumbersTheory
