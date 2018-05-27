import java.util.Random;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
    predicate ProbeInv(Probe p;) =
       p.value |-> ?v &*&
       p.sensor |-> ?s &*&
       s != null &*&
       SensorInv(s) &*&
       p.ran |-> ?r &*&
       r != null;
@*/


class Probe implements Runnable
{
   //@ predicate pre() = ProbeInv(this);
   //@ predicate post() = true;


    int value = 0;
   
    
    SensorInt sensor;
    Random ran;
    

    public Probe(SensorInt sensor)
    //@ requires sensor != null &*& SensorInv(sensor);
    //@ ensures pre();
    {
    	ran = new Random();
        this.sensor = sensor;
        this.value = ran.nextInt(sensor.max - sensor.min + 1) + sensor.min;
    }



    public void run()
    //@ requires pre();
    //@ ensures post();
    {
    
        while( true )
        //@ invariant ProbeInv(this);
        {
           // produce a new value every 2 seconds
           value = ran.nextInt(sensor.max - sensor.min + 1) + sensor.min;
           sensor.set(value);
           //sleep(2000);
           // Enter in a 2 second sleep, beware of thread sleeps in future
           // Requires change of javaspec to the TimeUnit class (check document)
           
        }
    }

}