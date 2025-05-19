import SystemE
import Smt.Real


-- set_option trace.smt true

namespace Elements.Book1

theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
  euclid_intros
  obtain ⟨BCD, h1⟩ := circle_from_points a b (by esmt)
  obtain ⟨ACE, h2⟩ := circle_from_points b a (by esmt)
  obtain ⟨c, hc⟩ := intersection_circles BCD ACE (by esmt)
  have hBCD := point_on_circle_onlyif a b c BCD (by esmt)
  have hACE := point_on_circle_onlyif b a c ACE (by esmt [h1, h2, hc])
  use c
  esmt [h1, h2, hc, hBCD, hACE]


theorem proposition_1' : ∀ (a b x : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

#print axioms proposition_1'
-- 'Elements.Book1.proposition_1'' depends on axioms: [Circle,
--  Line,
--  Point,
--  angle_range,
--  angle_symm,
--  area_congruence,
--  area_gte_zero,
--  area_symm_1,
--  area_symm_2,
--  between_if,
--  between_not_trans,
--  between_points,
--  between_same_line_in,
--  between_same_line_out,
--  between_symm,
--  between_trans_in,
--  between_trans_out,
--  center_inside_circle,
--  centre_unique,
--  circle_from_points,
--  circle_line_intersections,
--  circle_points_between,
--  circle_points_extend,
--  circles_intersections_diff_side,
--  degenerated_angle_if,
--  degenerated_angle_onlyif,
--  degenerated_area,
--  degenerated_area_if,
--  degenerated_area_onlyif,
--  equal_angles,
--  equal_circles,
--  flat_angle_if,
--  flat_angle_onlyif,
--  inside_not_on_circle,
--  intersection_circle_circle_1,
--  intersection_circle_circle_2,
--  intersection_circle_line_1,
--  intersection_circle_line_2,
--  intersection_lines_common_point,
--  intersection_lines_opposing,
--  intersection_opposite_side,
--  intersection_symm,
--  lines_intersect,
--  parallel_line_unique,
--  parallelogram_area,
--  parallelogram_same_side,
--  pasch_1,
--  pasch_2,
--  pasch_3,
--  pasch_4,
--  perpendicular_if,
--  perpendicular_onlyif,
--  point_in_circle_if,
--  point_in_circle_onlyif,
--  point_on_circle_if,
--  point_on_circle_onlyif,
--  propext,
--  rectangle_area,
--  same_side_not_on_line,
--  same_side_pigeon_hole,
--  same_side_rfl,
--  same_side_symm,
--  same_side_trans,
--  segment_gte_zero,
--  segment_symmetric,
--  sum_angles_if,
--  sum_angles_onlyif,
--  sum_areas_if,
--  sum_areas_onlyif,
--  sum_parallelograms_area,
--  superposition,
--  triple_incidence_1,
--  triple_incidence_2,
--  triple_incidence_3,
--  two_points_determine_line,
--  zero_segment_if,
--  zero_segment_onlyif,
--  Classical.choice,
--  Quot.sound]

end Elements.Book1
