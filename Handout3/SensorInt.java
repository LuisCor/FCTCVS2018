import java.util.Random;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
    predicate SensorInv(SensorInt s;) =
       s.value |-> ?v &*&
       s.max |-> ?m &*&
       s.min |-> ?n &*&
       m > n
       //s.mon |-> ?l &*&
       //l != null
       ;
@*/


class SensorInt
{

    ////@ predicate pre() = SensorInv(this);
    ////@ predicate post() = true;

    int value;
    int min;
    int max;
    
    ReentrantLock mon;
    Thread th;

    
    static final int SAMPLING = 3;
    
    SensorInt(int min, int max) 
    //@ requires max > min;
    //@ ensures SensorInv(this);
    {
        this.min = min;
        this.max = max;
        this.value = min;
        //this.th = new Thread(new Probe(this));
        //this.th.start();
    }
    
    
    int getMax()
    //@ requires SensorInv(this);
    //@ ensures true;
    { 
        return this.max;
    }  
    
    int getMin() 
    //@ requires SensorInv(this);
    //@ ensures true;    
    { 
        return this.min;
    }  
    
    int get() 
    { 
        return this.value;
    }    
    
    void set(int value)
    //@ requires SensorInv(this);
    //@ ensures SensorInv(this); 
    {
        this.value = value;
    }
    
    public static void main(String args[]) throws InterruptedException
    {
        SensorInt s = new SensorInt(0,10);
        
        while(true)
        {
            // get and print a sample every 5 seconds
            System.out.println("Value: " + value);
            sleep(5000);
            
        }
    }
}