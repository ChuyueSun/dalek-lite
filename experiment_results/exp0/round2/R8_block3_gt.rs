        proof {
            // completed → extended conversion preserves affine meaning
            assert(edwards_point_as_affine(result) == completed_point_as_affine_edwards(doubled));

            // And from the lower-level double() spec:
            assert(completed_point_as_affine_edwards(doubled) == edwards_double(
                edwards_point_as_affine(*self).0,
                edwards_point_as_affine(*self).1,
            ));
        }
