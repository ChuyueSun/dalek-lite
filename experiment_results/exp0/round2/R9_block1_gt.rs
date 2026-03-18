        proof {
            assert(choice_is_true(is_valid_y_coord) ==> is_valid_edwards_y_coordinate(
                field_element_from_bytes(&self.0),
            ));
            assert(choice_is_true(is_valid_y_coord) ==> is_on_edwards_curve(
                fe51_as_canonical_nat(&X),
                fe51_as_canonical_nat(&Y),
            ));
        }
