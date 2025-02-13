package edu.cmu.cs.ls.keymaerax.tags;

import org.scalatest.TagAnnotation;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@TagAnnotation
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE})
public @interface ExtremeTest {
    /** 3 hour default timeout. */
    int timeout() default 3;
}
