import java.util.Random;
import java.util.concurrent.*;

/*@
    predicate ProbeInv(Probe p; int v) =
       p.value |-> v &*&
       p.sensor |-> ?s &*&
       s != null &*&
       p.max |-> ?m &*&
       p.min |-> ?n &*&
       p.ran |-> ?r &*&
       r != null &*&
       m > n &*&
       m > v &*&
       v > n;
@*/


class Probe implements Runnable
{
   
    //@ predicate pre() = ProbeInv(this, ?v);
    //@ predicate post() = true;

    int max = 0;
    int min = 0;
    int value = 0;
   
    
    SensorInt sensor;
    Random ran;
    

    public Probe(SensorInt sensor)
    //@ requires sensor != null &*& SensorInv(sensor, ?v);
    //@ ensures true;
    {
    	ran = new Random();
        this.sensor = sensor;
        this.max = sensor.getMax();
        this.min = sensor.getMin();
        this.value = ran.nextInt(max - min + 1) + min;
    }



    public void run()
    //@ requires pre() &*& SensorInv(sensor, ?v);
    //@ ensures post();
    {
    
        while( true )
        //@ invariant ProbeInv(this, ?v);
        {
           // produce a new value every 2 seconds
           value = ran.nextInt(max - min + 1) + min;
           sensor.set(value);
           //sleep(2000);
           // Enter in a 2 second sleep, beware of thread sleeps in future
           // Requires change of javaspec to the TimeUnit class (check document)
           
        }
    }

}